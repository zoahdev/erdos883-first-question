import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_76 :
    (List.ofFn coreChunks462_76).flatten =
      (coreData462.take (coreResources462 76).q).drop 152 := by
  decide +kernel

theorem coreCheck462_76 :
    ∀ c : Fin 1, (coreChunks462_76 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 76)) = true := by
  decide +kernel
#print axioms coreFlatten462_76
#print axioms coreCheck462_76
end Erdos883Verified
