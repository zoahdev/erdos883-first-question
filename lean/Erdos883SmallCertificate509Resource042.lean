import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_42 :
    (List.ofFn coreChunks509_42).flatten =
      (coreData509.take (coreResources509 42).q).drop 86 := by
  decide +kernel

theorem coreCheck509_42 :
    ∀ c : Fin 1, (coreChunks509_42 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 42)) = true := by
  decide +kernel
#print axioms coreFlatten509_42
#print axioms coreCheck509_42
end Erdos883Verified
