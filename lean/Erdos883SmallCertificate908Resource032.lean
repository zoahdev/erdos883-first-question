import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_32 :
    (List.ofFn coreChunks908_32).flatten =
      (coreData908.take (coreResources908 32).q).drop 181 := by
  decide +kernel

theorem coreCheck908_32 :
    ∀ c : Fin 1, (coreChunks908_32 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 32)) = true := by
  decide +kernel
#print axioms coreFlatten908_32
#print axioms coreCheck908_32
end Erdos883Verified
