import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_19 :
    (List.ofFn coreChunks509_19).flatten =
      (coreData509.take (coreResources509 19).q).drop 109 := by
  decide +kernel

theorem coreCheck509_19 :
    ∀ c : Fin 1, (coreChunks509_19 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 19)) = true := by
  decide +kernel
#print axioms coreFlatten509_19
#print axioms coreCheck509_19
end Erdos883Verified
