import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_61 :
    (List.ofFn coreChunks462_61).flatten =
      (coreData462.take (coreResources462 61).q).drop 114 := by
  decide +kernel

theorem coreCheck462_61 :
    ∀ c : Fin 1, (coreChunks462_61 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 61)) = true := by
  decide +kernel
#print axioms coreFlatten462_61
#print axioms coreCheck462_61
end Erdos883Verified
