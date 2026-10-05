import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_43 :
    (List.ofFn coreChunks509_43).flatten =
      (coreData509.take (coreResources509 43).q).drop 87 := by
  decide +kernel

theorem coreCheck509_43 :
    ∀ c : Fin 1, (coreChunks509_43 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 43)) = true := by
  decide +kernel
#print axioms coreFlatten509_43
#print axioms coreCheck509_43
end Erdos883Verified
