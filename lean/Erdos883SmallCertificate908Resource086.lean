import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_86 :
    (List.ofFn coreChunks908_86).flatten =
      (coreData908.take (coreResources908 86).q).drop 155 := by
  decide +kernel

theorem coreCheck908_86 :
    ∀ c : Fin 1, (coreChunks908_86 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 86)) = true := by
  decide +kernel
#print axioms coreFlatten908_86
#print axioms coreCheck908_86
end Erdos883Verified
