import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_53 :
    (List.ofFn coreChunks509_53).flatten =
      (coreData509.take (coreResources509 53).q).drop 101 := by
  decide +kernel

theorem coreCheck509_53 :
    ∀ c : Fin 1, (coreChunks509_53 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 53)) = true := by
  decide +kernel
#print axioms coreFlatten509_53
#print axioms coreCheck509_53
end Erdos883Verified
