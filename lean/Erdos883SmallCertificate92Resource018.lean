import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_18 :
    (List.ofFn coreChunks92_18).flatten =
      (coreData92.take (coreResources92 18).q).drop 28 := by
  decide +kernel

theorem coreCheck92_18 :
    ∀ c : Fin 1, (coreChunks92_18 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 18)) = true := by
  decide +kernel
#print axioms coreFlatten92_18
#print axioms coreCheck92_18
end Erdos883Verified
