import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_73 :
    (List.ofFn coreChunks462_73).flatten =
      (coreData462.take (coreResources462 73).q).drop 141 := by
  decide +kernel

theorem coreCheck462_73 :
    ∀ c : Fin 1, (coreChunks462_73 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 73)) = true := by
  decide +kernel
#print axioms coreFlatten462_73
#print axioms coreCheck462_73
end Erdos883Verified
