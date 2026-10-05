import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_45 :
    (List.ofFn coreChunks462_45).flatten =
      (coreData462.take (coreResources462 45).q).drop 91 := by
  decide +kernel

theorem coreCheck462_45 :
    ∀ c : Fin 1, (coreChunks462_45 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 45)) = true := by
  decide +kernel
#print axioms coreFlatten462_45
#print axioms coreCheck462_45
end Erdos883Verified
