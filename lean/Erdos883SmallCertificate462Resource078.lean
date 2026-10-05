import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_78 :
    (List.ofFn coreChunks462_78).flatten =
      (coreData462.take (coreResources462 78).q).drop 166 := by
  decide +kernel

theorem coreCheck462_78 :
    ∀ c : Fin 1, (coreChunks462_78 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 78)) = true := by
  decide +kernel
#print axioms coreFlatten462_78
#print axioms coreCheck462_78
end Erdos883Verified
