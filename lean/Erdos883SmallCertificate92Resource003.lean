import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_3 :
    (List.ofFn coreChunks92_3).flatten =
      (coreData92.take (coreResources92 3).q).drop 13 := by
  decide +kernel

theorem coreCheck92_3 :
    ∀ c : Fin 1, (coreChunks92_3 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 3)) = true := by
  decide +kernel
#print axioms coreFlatten92_3
#print axioms coreCheck92_3
end Erdos883Verified
