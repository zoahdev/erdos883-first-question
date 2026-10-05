import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_5 :
    (List.ofFn coreChunks92_5).flatten =
      (coreData92.take (coreResources92 5).q).drop 18 := by
  decide +kernel

theorem coreCheck92_5 :
    ∀ c : Fin 1, (coreChunks92_5 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 5)) = true := by
  decide +kernel
#print axioms coreFlatten92_5
#print axioms coreCheck92_5
end Erdos883Verified
