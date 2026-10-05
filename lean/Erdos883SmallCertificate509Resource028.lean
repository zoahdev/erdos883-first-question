import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_28 :
    (List.ofFn coreChunks509_28).flatten =
      (coreData509.take (coreResources509 28).q).drop 123 := by
  decide +kernel

theorem coreCheck509_28 :
    ∀ c : Fin 1, (coreChunks509_28 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 28)) = true := by
  decide +kernel
#print axioms coreFlatten509_28
#print axioms coreCheck509_28
end Erdos883Verified
