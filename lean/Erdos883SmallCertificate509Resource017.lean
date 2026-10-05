import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_17 :
    (List.ofFn coreChunks509_17).flatten =
      (coreData509.take (coreResources509 17).q).drop 107 := by
  decide +kernel

theorem coreCheck509_17 :
    ∀ c : Fin 1, (coreChunks509_17 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 17)) = true := by
  decide +kernel
#print axioms coreFlatten509_17
#print axioms coreCheck509_17
end Erdos883Verified
