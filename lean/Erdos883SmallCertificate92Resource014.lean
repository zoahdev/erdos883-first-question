import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_14 :
    (List.ofFn coreChunks92_14).flatten =
      (coreData92.take (coreResources92 14).q).drop 35 := by
  decide +kernel

theorem coreCheck92_14 :
    ∀ c : Fin 1, (coreChunks92_14 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 14)) = true := by
  decide +kernel
#print axioms coreFlatten92_14
#print axioms coreCheck92_14
end Erdos883Verified
