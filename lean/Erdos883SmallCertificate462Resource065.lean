import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_65 :
    (List.ofFn coreChunks462_65).flatten =
      (coreData462.take (coreResources462 65).q).drop 120 := by
  decide +kernel

theorem coreCheck462_65 :
    ∀ c : Fin 1, (coreChunks462_65 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 65)) = true := by
  decide +kernel
#print axioms coreFlatten462_65
#print axioms coreCheck462_65
end Erdos883Verified
