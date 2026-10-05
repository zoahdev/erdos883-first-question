import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_77 :
    (List.ofFn coreChunks462_77).flatten =
      (coreData462.take (coreResources462 77).q).drop 157 := by
  decide +kernel

theorem coreCheck462_77 :
    ∀ c : Fin 1, (coreChunks462_77 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 77)) = true := by
  decide +kernel
#print axioms coreFlatten462_77
#print axioms coreCheck462_77
end Erdos883Verified
