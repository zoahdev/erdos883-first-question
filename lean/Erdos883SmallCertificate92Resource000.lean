import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_0 :
    (List.ofFn coreChunks92_0).flatten =
      (coreData92.take (coreResources92 0).q).drop 0 := by
  decide +kernel

theorem coreCheck92_0 :
    ∀ c : Fin 1, (coreChunks92_0 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 0)) = true := by
  decide +kernel
#print axioms coreFlatten92_0
#print axioms coreCheck92_0
end Erdos883Verified
