import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_4 :
    (List.ofFn coreChunks92_4).flatten =
      (coreData92.take (coreResources92 4).q).drop 17 := by
  decide +kernel

theorem coreCheck92_4 :
    ∀ c : Fin 1, (coreChunks92_4 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 4)) = true := by
  decide +kernel
#print axioms coreFlatten92_4
#print axioms coreCheck92_4
end Erdos883Verified
