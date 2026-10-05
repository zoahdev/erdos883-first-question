import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_9 :
    (List.ofFn coreChunks92_9).flatten =
      (coreData92.take (coreResources92 9).q).drop 23 := by
  decide +kernel

theorem coreCheck92_9 :
    ∀ c : Fin 1, (coreChunks92_9 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 9)) = true := by
  decide +kernel
#print axioms coreFlatten92_9
#print axioms coreCheck92_9
end Erdos883Verified
