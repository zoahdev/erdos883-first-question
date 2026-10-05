import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_81 :
    (List.ofFn coreChunks462_81).flatten =
      (coreData462.take (coreResources462 81).q).drop 192 := by
  decide +kernel

theorem coreCheck462_81 :
    ∀ c : Fin 1, (coreChunks462_81 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 81)) = true := by
  decide +kernel
#print axioms coreFlatten462_81
#print axioms coreCheck462_81
end Erdos883Verified
