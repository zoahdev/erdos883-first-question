import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_8 :
    (List.ofFn coreChunks92_8).flatten =
      (coreData92.take (coreResources92 8).q).drop 21 := by
  decide +kernel

theorem coreCheck92_8 :
    ∀ c : Fin 1, (coreChunks92_8 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 8)) = true := by
  decide +kernel
#print axioms coreFlatten92_8
#print axioms coreCheck92_8
end Erdos883Verified
