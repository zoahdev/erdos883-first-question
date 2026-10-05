import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_12 :
    (List.ofFn coreChunks92_12).flatten =
      (coreData92.take (coreResources92 12).q).drop 28 := by
  decide +kernel

theorem coreCheck92_12 :
    ∀ c : Fin 1, (coreChunks92_12 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 12)) = true := by
  decide +kernel
#print axioms coreFlatten92_12
#print axioms coreCheck92_12
end Erdos883Verified
