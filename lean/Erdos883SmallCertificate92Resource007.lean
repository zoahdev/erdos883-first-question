import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_7 :
    (List.ofFn coreChunks92_7).flatten =
      (coreData92.take (coreResources92 7).q).drop 20 := by
  decide +kernel

theorem coreCheck92_7 :
    ∀ c : Fin 1, (coreChunks92_7 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 7)) = true := by
  decide +kernel
#print axioms coreFlatten92_7
#print axioms coreCheck92_7
end Erdos883Verified
