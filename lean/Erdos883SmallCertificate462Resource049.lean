import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_49 :
    (List.ofFn coreChunks462_49).flatten =
      (coreData462.take (coreResources462 49).q).drop 97 := by
  decide +kernel

theorem coreCheck462_49 :
    ∀ c : Fin 1, (coreChunks462_49 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 49)) = true := by
  decide +kernel
#print axioms coreFlatten462_49
#print axioms coreCheck462_49
end Erdos883Verified
