import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_1 :
    (List.ofFn coreChunks92_1).flatten =
      (coreData92.take (coreResources92 1).q).drop 0 := by
  decide +kernel

theorem coreCheck92_1 :
    ∀ c : Fin 1, (coreChunks92_1 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 1)) = true := by
  decide +kernel
#print axioms coreFlatten92_1
#print axioms coreCheck92_1
end Erdos883Verified
