import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_68 :
    (List.ofFn coreChunks462_68).flatten =
      (coreData462.take (coreResources462 68).q).drop 125 := by
  decide +kernel

theorem coreCheck462_68 :
    ∀ c : Fin 1, (coreChunks462_68 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 68)) = true := by
  decide +kernel
#print axioms coreFlatten462_68
#print axioms coreCheck462_68
end Erdos883Verified
