import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_19 :
    (List.ofFn coreChunks92_19).flatten =
      (coreData92.take (coreResources92 19).q).drop 29 := by
  decide +kernel

theorem coreCheck92_19 :
    ∀ c : Fin 1, (coreChunks92_19 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 19)) = true := by
  decide +kernel
#print axioms coreFlatten92_19
#print axioms coreCheck92_19
end Erdos883Verified
