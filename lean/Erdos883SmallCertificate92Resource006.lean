import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_6 :
    (List.ofFn coreChunks92_6).flatten =
      (coreData92.take (coreResources92 6).q).drop 19 := by
  decide +kernel

theorem coreCheck92_6 :
    ∀ c : Fin 1, (coreChunks92_6 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 6)) = true := by
  decide +kernel
#print axioms coreFlatten92_6
#print axioms coreCheck92_6
end Erdos883Verified
