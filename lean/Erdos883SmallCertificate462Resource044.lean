import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_44 :
    (List.ofFn coreChunks462_44).flatten =
      (coreData462.take (coreResources462 44).q).drop 90 := by
  decide +kernel

theorem coreCheck462_44 :
    ∀ c : Fin 1, (coreChunks462_44 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 44)) = true := by
  decide +kernel
#print axioms coreFlatten462_44
#print axioms coreCheck462_44
end Erdos883Verified
