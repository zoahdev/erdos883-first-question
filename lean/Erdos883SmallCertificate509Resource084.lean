import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_84 :
    (List.ofFn coreChunks509_84).flatten =
      (coreData509.take (coreResources509 84).q).drop 173 := by
  decide +kernel

theorem coreCheck509_84 :
    ∀ c : Fin 1, (coreChunks509_84 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 84)) = true := by
  decide +kernel
#print axioms coreFlatten509_84
#print axioms coreCheck509_84
end Erdos883Verified
