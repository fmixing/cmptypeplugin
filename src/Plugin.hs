{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE ExplicitNamespaces   #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE ExplicitForAll       #-}

module Plugin (plugin, CmpType) where

import           Data.Either         (rights)
import           Data.Maybe          (catMaybes)
import           Data.Type.Equality  (type (==))
import           Data.Typeable       (Proxy(..), Proxy, Typeable(..), typeRepFingerprint)
import           Debug.Trace         (trace)
import           GHC.TcPluginM.Extra (evByFiat, lookupModule, lookupName, tracePlugin)
import           Outputable          (Outputable, ppr, showSDocUnsafe)
import qualified       Data.Kind           (Type)
import Type.Reflection (TypeRep, typeRep, typeOf)


-- GHC API
import           FastString          (fsLit)
import           Module              (mkModuleName, Module(Module), moduleNameString, unitIdString, moduleName, moduleUnitId)
import           Name                (getName, nameOccName, nameModule)
import           OccName             (mkTcOcc, occNameString)
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
import GHC.Fingerprint.Type (Fingerprint(..))
import GHC.Fingerprint (fingerprintString, fingerprintFingerprints)

type family CmpType (a :: k) (b :: k) :: Ordering

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = const (Just cmpTypePlugin) }

cmpTypePlugin :: TcPlugin
cmpTypePlugin =
  TcPlugin { tcPluginInit  = trace "apply tcPluginInit" $ return Nothing
           , tcPluginSolve = solveCmp
           , tcPluginStop  = const (return ())
           }

solveCmp :: Maybe a
         -> [Ct]
         -> [Ct]
         -> [Ct]
         -> TcPluginM TcPluginResult
solveCmp _ _ _ wanteds = do
    let setConstraints = printCt wanteds
    case trace "apply tcPluginSolve" setConstraints of
        [] -> return $ TcPluginOk [] []
        _ -> return $ TcPluginContradiction []

-- typeRepFingerprint (typeRep @Bool)
-- ebf3a8541b05453b8bcac4a38e8b80a4
-- ebf3a8541b05453b8bcac4a38e8b80a4

-- typeRepFingerprint (typeRep @[Int, Bool])
-- fd08774aff73e44470311a620583e0ae
-- 

-- typeRepFingerprint (typeRep @[Int])
-- f7ea91875ddd888c2b4aa73e9744c883
-- f7ea91875ddd888c2b4aa73e9744c883

-- typeRepFingerprint (typeRep @(Either Int Bool))
-- 8a39e35c00246e54d9a5de881c250ce8
-- 8a39e35c00246e54d9a5de881c250ce8

-- typeRepFingerprint (typeRep @('[Int]))
-- 3514f55408d6e3846ca4277591763b7c
-- 574bc2b6ebf6c8717d388cad922cfef9

printCt :: [Ct] -> [Ct]
printCt [] = trace "Empty list" []
printCt (x : xs) = do
    let [_, _, cmp, _] = getKOT $ getType x
    let [_, t1, t2] = getKOT cmp

    let kot1 = getKOT t1
    let kot2 = getKOT t2

    let fgp1 = trace "make t1 fingerprint" makeTyConFingerprint t1
    let fgp2 = trace "make t2 fingerprint" makeTyConFingerprint t2

    trace ("fpr t1: " ++ (show fgp1) ++ " kot1: " ++ (showSDocUnsafe $ ppr kot1) ++ " fpr t2: " ++ (show fgp2) ++ " kot2: " ++ (showSDocUnsafe $ ppr kot2)) (x : printCt xs)

getKOT :: Type -> [Type]
getKOT (TyConApp _ kot) = kot

composeFgp :: Fingerprint -> [Fingerprint] -> Fingerprint
composeFgp fgp [] = fgp
composeFgp fgp (x : xs) = composeFgp (fingerprintFingerprints [fgp, x]) xs

makeTyConFingerprint :: Type -> Fingerprint
makeTyConFingerprint t = do
    let ty_con_fgp = getTyConFingerprint $ getTyCon t
    let kot = getKOT t
    let fgpkot = map makeTyConFingerprint kot
    trace (" kot: " ++ (showSDocUnsafe $ ppr kot)) $ composeFgp ty_con_fgp fgpkot

getType :: Ct -> Type
getType ct = ctEvPred $ ctEvidence ct 

getTyCon :: Type -> TyCon
getTyCon (TyConApp tyCon _) = tyCon

getTyConFingerprint :: TyCon -> Fingerprint
getTyConFingerprint tyCon = do
    let mod_name = nameModule $ getName tyCon
    let mod_fpr = moduleNameString $ moduleName mod_name
    let pkg_fpr = unitIdString $ moduleUnitId mod_name
    let n = occNameString $ nameOccName $ getName tyCon
    trace (" name: "  ++ (pkg_fpr ++ " " ++ mod_fpr ++ " " ++ n)) $ fingerprintFingerprints $ [mkTyConFingerprint pkg_fpr mod_fpr n]

mkTyConFingerprint :: String -- ^ package name
                   -> String -- ^ module name
                   -> String -- ^ tycon name
                   -> Fingerprint
mkTyConFingerprint pkg_name mod_name tycon_name =
        fingerprintFingerprints
        [ fingerprintString pkg_name
        , fingerprintString mod_name
        , fingerprintString tycon_name
        ]


-- trTYPE :: TypeRep TYPE
-- trTYPE = typeRep

-- trLiftedRep :: TypeRep 'LiftedRep
-- trLiftedRep = typeRep

-- mkTrType :: TypeRep Type
-- mkTrType = TrType

-- typeRepFingerprint :: TypeRep a -> Fingerprint
-- typeRepFingerprint TrType = fpTYPELiftedRep
-- typeRepFingerprint (TrTyCon {trTyConFingerprint = fpr}) = fpr
-- typeRepFingerprint (TrApp {trAppFingerprint = fpr}) = fpr
-- typeRepFingerprint (TrFun {trFunFingerprint = fpr}) = fpr

-- fpTYPELiftedRep :: Fingerprint
-- fpTYPELiftedRep = fingerprintFingerprints
--       [tyConFingerprint tyConTYPE, typeRepFingerprint trLiftedRep]

func' :: Type -> String
func' (TyVarTy var) = "TyVarTy " ++ (show $ isId var) ++ (show $ isTyVar var) ++ (show $ isTcTyVar var) ++ " "  ++ (showSDocUnsafe $ pprTcTyVarDetails $ tcTyVarDetails var) ++ " " ++ (showSDocUnsafe $ ppr var) ++ " "
func' AppTy{} = "AppTy "
func' ForAllTy{} = "ForAllTy "
func' FunTy{} = "FunTy "
func' LitTy{} = "LitTy "
func' CastTy{} = "CastTy "
func' CoercionTy{} = "CoercionTy "
func' (TyConApp tyCon kot) = "TyConApp: tyConFlavour: " ++ (tyConFlavour tyCon) ++ ", sDoc: " ++ (showSDocUnsafe $ ppr tyCon) ++ ", KindsOrTypes: " ++ (showSDocUnsafe $ ppr kot) ++ ":: " ++ (show $ fmap func' kot)