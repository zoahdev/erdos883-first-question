import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_9 :
    (List.ofFn coreChunks509_9).flatten =
      (coreData509.take (coreResources509 9).q).drop 98 := by
  decide +kernel

theorem coreCheck509_9 :
    ∀ c : Fin 1, (coreChunks509_9 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 9)) = true := by
  decide +kernel
#print axioms coreFlatten509_9
#print axioms coreCheck509_9
end Erdos883Verified
