import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_35 :
    (List.ofFn coreChunks462_35).flatten =
      (coreData462.take (coreResources462 35).q).drop 77 := by
  decide +kernel

theorem coreCheck462_35 :
    ∀ c : Fin 1, (coreChunks462_35 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 35)) = true := by
  decide +kernel
#print axioms coreFlatten462_35
#print axioms coreCheck462_35
end Erdos883Verified
