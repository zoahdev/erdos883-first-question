import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_13 :
    (List.ofFn coreChunks462_13).flatten =
      (coreData462.take (coreResources462 13).q).drop 97 := by
  decide +kernel

theorem coreCheck462_13 :
    ∀ c : Fin 1, (coreChunks462_13 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 13)) = true := by
  decide +kernel
#print axioms coreFlatten462_13
#print axioms coreCheck462_13
end Erdos883Verified
