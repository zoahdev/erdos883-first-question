import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_69 :
    (List.ofFn coreChunks462_69).flatten =
      (coreData462.take (coreResources462 69).q).drop 130 := by
  decide +kernel

theorem coreCheck462_69 :
    ∀ c : Fin 1, (coreChunks462_69 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 69)) = true := by
  decide +kernel
#print axioms coreFlatten462_69
#print axioms coreCheck462_69
end Erdos883Verified
