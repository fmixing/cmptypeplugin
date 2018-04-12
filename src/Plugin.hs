{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE ExplicitNamespaces   #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE ExplicitForAll       #-}

module Plugin ( plugin, CmpType ) where

import           Data.Either         (rights)
import           Data.Maybe          (catMaybes)
import           Data.Type.Equality  (type (==))
import           Data.Typeable       (Proxy(..), Proxy, TypeRep, Typeable(..), typeRep, typeOf, typeRepFingerprint)
import           Debug.Trace         (trace)
import           GHC.TcPluginM.Extra (evByFiat, lookupModule, lookupName, tracePlugin)
import           Outputable          (Outputable, ppr, showSDocUnsafe)
import           Data.Type.Set       (Cmp)


-- GHC API
import           FastString          (fsLit)
import           Module              (mkModuleName)
import           Name                (getName)
import           OccName             (mkTcOcc)
import           Plugins             (Plugin (..), defaultPlugin)
import           TcEvidence          (EvTerm (..))
import           TcPluginM           (TcPluginM, tcLookupTyCon, zonkCt, tcPluginTrace)
import           TcRnTypes           (Ct, TcPlugin (..), TcPluginResult (..),
                                      ctEvPred, ctEvidence)
import           TcType              (pprTcTyVarDetails)
import           TyCon               (TyCon (..), isPromotedDataCon,
                                      tyConBinders, tyConFlavour, tyConName,
                                      tyConUnique, isFamilyTyCon)
import           TyCoRep             (KindOrType, Type (..))
import           Type                (EqRel (..), PredTree (..),
                                      classifyPredType, isTyVarTy, nonDetCmpType)
import           Var                 (isId, isTcTyVar, isTyVar, tcTyVarDetails)
import           Unique              (getKey, getUnique)
import           TysWiredIn          (listTyCon, consDataCon)
import           TcHsType            (tcInferArgs)

-- type family Cmp (a :: k) (b :: k) :: Ordering

-- type instance Cmp (a :: Type) (b :: Type) = 
    
type family CmpType (a :: Type) (b :: Type) :: Ordering

type instance Cmp (a :: Type) (b :: Type) = CmpType a b

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = const (Just cmpTypePlugin) }

cmpTypePlugin :: TcPlugin
cmpTypePlugin =
  TcPlugin { tcPluginInit  = lookupCmpTyCon
           , tcPluginSolve = solveCmp
           , tcPluginStop  = const (return ())
           }

lookupCmpTyCon :: TcPluginM CmpDef
lookupCmpTyCon = do
    md <- lookupModule cmpModule cmpPackage
    cmpTyCon <- look md "CmpType"
    return $ CmpDef cmpTyCon
  where
    cmpModule = mkModuleName "Plugin"
    cmpPackage = fsLit "cmptypeplugin"
    look md s = tcLookupTyCon =<< lookupName md (mkTcOcc s)

newtype CmpDef = CmpDef { cmp :: TyCon }

solveCmp :: CmpDef
         -> [Ct]
         -> [Ct]
         -> [Ct]
         -> TcPluginM TcPluginResult
solveCmp _ _ _ [] = return $ TcPluginOk [] []
solveCmp defs _ _ wanteds = do
    let setConstraints = catMaybes $ fmap (getSetConstraint defs) wanteds
    case setConstraints of
        [] -> return $ TcPluginOk [] []
        _ -> return $ TcPluginContradiction []

-- здесь KindsOrTypes == [*, '[Int, Bool, Int]] -- ' здесь из вывода (те аутпута)
-- constraintToEvTerm :: SetConstraint -> Either Ct ([(EvTerm, Ct)], [Ct])
-- constraintToEvTerm setConstraint = do
--     let (ct, ty1, ty2, _, _) = setConstraint
--     case ty1 of
--         (TyConApp _ [_, y1]) ->  -- первый _ это TyCon для типа, второй _ это *
--             case ty2 of
--                 (TyConApp _ [_, y2]) -> do
--                     let types1 = trace ("extracted1 " ++ (showSDocUnsafe $ ppr $ extractTypes y1) ++ " sorted1 " ++ (showSDocUnsafe $ ppr $ sort $ extractTypes y1)) sort $ extractTypes y1
--                     let types2 = trace ("extracted2 " ++ (showSDocUnsafe $ ppr $ extractTypes y2) ++ " sorted2 " ++ (showSDocUnsafe $ ppr $ sort $ extractTypes y2)) sort $ extractTypes y2
--                     if checkEquality types1 types2
--                         then trace ("typechecked: " ++ (showSDocUnsafe $ ppr $ ty1) ++ " ~ " ++ (showSDocUnsafe $ ppr $ ty2)) Right ([(evByFiat "set-constraint" ty1 ty2, ct)], [])
--                         else trace ("not typechecked: " ++ (showSDocUnsafe $ ppr $ ty1) ++ " /~ " ++ (showSDocUnsafe $ ppr $ ty2)) Left ct
--                 _ -> Right ([], [ct]) -- означает, что плагин не может решить данный констрейнт (в смысле не предназначен для решения)
--         _-> Right ([], [ct])

-- nonDetCmpType x y

checkEquality :: [Type] -> [Type] -> Bool
checkEquality [] [] = True
checkEquality _ [] = False
checkEquality [] _ = False
checkEquality (x : xs) (y : ys) = nonDetCmpType x y == EQ && checkEquality xs ys


-- data PredTree = ClassPred Class [Type]
--               | EqPred EqRel Type Type
--               | IrredPred PredType
-- data EqRel = NomEq | ReprEq deriving (Eq, Ord)
-- | A choice of equality relation. This is separate from the type 'Role'
-- because 'Phantom' does not define a (non-trivial) equality relation.

-- EqPred NomEq (ty1 :: TyConApp) (ty2 :: TyConApp)
-- TyConApp TyCon [KindOrType]
-- ty1 == TyConApp (Set :: TyCon) ([*, '[Int, Bool, Int]] :: [KindOrType]) для нашего случая
-- getSetConstraint :: CmpDef -> Ct -> Maybe SetConstraint
-- getSetConstraint defs ct =
--     case classifyPredType $ ctEvPred $ ctEvidence ct of
--         (EqPred NomEq ty1 ty2) -- NomEq == nominal equality
--             -> case ty1 of
--                 (TyConApp tyCon1 kot1) -> case ty2 of
--                     (TyConApp tyCon2 kot2)
--                         | tyConName tyCon1 == getName (set defs) && tyConName tyCon2 == getName (set defs) -> Just (ct, ty1, ty2, kot1, kot2)
--                     _ -> Nothing
--                 _ -> Nothing
--         _ -> Nothing

type SetConstraint = ( Ct    -- The Set constraint
                     , Type  -- Fst argument to equality constraint
                     , Type  -- Snd argument to equality constraint
                     , [KindOrType] -- типы для первого Set
                     , [KindOrType] -- типы для второго Set
                     )

-- DEBUG
getSetConstraint :: CmpDef -> Ct -> Maybe SetConstraint
getSetConstraint defs ct =
    -- case trace ((showSDocUnsafe $ ppr $ ctEvPred $ ctEvidence ct) ++ " " ++ (showSDocUnsafe $ ppr ct)) (classifyPredType $ ctEvPred $ ctEvidence ct) of
    case (classifyPredType $ ctEvPred $ ctEvidence ct) of
        (EqPred NomEq ty1 ty2) -- NomEq == nominal equality
            -- |  className cls == (getName $ knownRatTyCon defs)
            --    -> Just (ct, cls, ty)
            -- -> trace (showSDocUnsafe $ ppr a) Nothing
            -> case ty1 of
                (TyConApp tyCon1 kot1) -> case ty2 of
                    (TyConApp tyCon2 kot2) -> trace ("TyConApp " ++ (showSDocUnsafe $ ppr tyCon1) ++ " " ++ (showSDocUnsafe $ ppr kot1) ++ " " ++ (show $ fmap (\x -> (showSDocUnsafe $ ppr x) ++ "         " ++ func' x) kot1)) Nothing
                    _ -> Nothing
                _ -> Nothing
            -- -> trace (func' ty1 ++ " " ++ func' ty2) Nothing
        (ClassPred clz ty) -> trace ("ClassPred " ++ (showSDocUnsafe $ ppr clz) ++ " " ++ (showSDocUnsafe $ ppr ty)) Nothing
        IrredPred{} -> trace "IrredPred" Nothing

func' :: Type -> String
func' (TyVarTy var) = "TyVarTy " ++ (show $ isId var) ++ (show $ isTyVar var) ++ (show $ isTcTyVar var) ++ " "  ++ (showSDocUnsafe $ pprTcTyVarDetails $ tcTyVarDetails var) ++ " " ++ (showSDocUnsafe $ ppr var) ++ " "
func' AppTy{} = "AppTy "
func' ForAllTy{} = "ForAllTy "
func' FunTy{} = "FunTy "
func' LitTy{} = "LitTy "
func' CastTy{} = "CastTy "
func' CoercionTy{} = "CoercionTy "
func' (TyConApp tyCon kot) = "TyConApp: tyConFlavour: " ++ (tyConFlavour tyCon) ++ ", sDoc: " ++ (showSDocUnsafe $ ppr tyCon) ++ ", KindsOrTypes: " ++ (showSDocUnsafe $ ppr kot) ++ ":: " ++ (show $ fmap func' kot)