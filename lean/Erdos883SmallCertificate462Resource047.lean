import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_47 :
    (List.ofFn coreChunks462_47).flatten =
      (coreData462.take (coreResources462 47).q).drop 93 := by
  decide +kernel

theorem coreCheck462_47 :
    ∀ c : Fin 1, (coreChunks462_47 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 47)) = true := by
  decide +kernel
#print axioms coreFlatten462_47
#print axioms coreCheck462_47
end Erdos883Verified
