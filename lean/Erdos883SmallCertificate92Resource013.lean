import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_13 :
    (List.ofFn coreChunks92_13).flatten =
      (coreData92.take (coreResources92 13).q).drop 31 := by
  decide +kernel

theorem coreCheck92_13 :
    ∀ c : Fin 1, (coreChunks92_13 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 13)) = true := by
  decide +kernel
#print axioms coreFlatten92_13
#print axioms coreCheck92_13
end Erdos883Verified
