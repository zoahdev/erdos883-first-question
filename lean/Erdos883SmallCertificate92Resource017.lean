import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_17 :
    (List.ofFn coreChunks92_17).flatten =
      (coreData92.take (coreResources92 17).q).drop 0 := by
  decide +kernel

theorem coreCheck92_17 :
    ∀ c : Fin 2, (coreChunks92_17 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 17)) = true := by
  decide +kernel
#print axioms coreFlatten92_17
#print axioms coreCheck92_17
end Erdos883Verified
