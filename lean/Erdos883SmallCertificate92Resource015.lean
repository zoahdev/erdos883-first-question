import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_15 :
    (List.ofFn coreChunks92_15).flatten =
      (coreData92.take (coreResources92 15).q).drop 37 := by
  decide +kernel

theorem coreCheck92_15 :
    ∀ c : Fin 1, (coreChunks92_15 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 15)) = true := by
  decide +kernel
#print axioms coreFlatten92_15
#print axioms coreCheck92_15
end Erdos883Verified
