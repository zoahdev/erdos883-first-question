import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_38 :
    (List.ofFn coreChunks462_38).flatten =
      (coreData462.take (coreResources462 38).q).drop 80 := by
  decide +kernel

theorem coreCheck462_38 :
    ∀ c : Fin 1, (coreChunks462_38 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 38)) = true := by
  decide +kernel
#print axioms coreFlatten462_38
#print axioms coreCheck462_38
end Erdos883Verified
