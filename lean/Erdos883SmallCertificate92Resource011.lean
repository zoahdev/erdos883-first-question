import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_11 :
    (List.ofFn coreChunks92_11).flatten =
      (coreData92.take (coreResources92 11).q).drop 27 := by
  decide +kernel

theorem coreCheck92_11 :
    ∀ c : Fin 1, (coreChunks92_11 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 11)) = true := by
  decide +kernel
#print axioms coreFlatten92_11
#print axioms coreCheck92_11
end Erdos883Verified
