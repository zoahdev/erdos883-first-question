import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_2 :
    (List.ofFn coreChunks92_2).flatten =
      (coreData92.take (coreResources92 2).q).drop 12 := by
  decide +kernel

theorem coreCheck92_2 :
    ∀ c : Fin 1, (coreChunks92_2 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 2)) = true := by
  decide +kernel
#print axioms coreFlatten92_2
#print axioms coreCheck92_2
end Erdos883Verified
