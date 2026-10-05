import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_20 :
    (List.ofFn coreChunks462_20).flatten =
      (coreData462.take (coreResources462 20).q).drop 104 := by
  decide +kernel

theorem coreCheck462_20 :
    ∀ c : Fin 1, (coreChunks462_20 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 20)) = true := by
  decide +kernel
#print axioms coreFlatten462_20
#print axioms coreCheck462_20
end Erdos883Verified
