import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_10 :
    (List.ofFn coreChunks92_10).flatten =
      (coreData92.take (coreResources92 10).q).drop 25 := by
  decide +kernel

theorem coreCheck92_10 :
    ∀ c : Fin 1, (coreChunks92_10 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 10)) = true := by
  decide +kernel
#print axioms coreFlatten92_10
#print axioms coreCheck92_10
end Erdos883Verified
