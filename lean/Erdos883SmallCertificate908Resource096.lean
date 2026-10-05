import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_96 :
    (List.ofFn coreChunks908_96).flatten =
      (coreData908.take (coreResources908 96).q).drop 169 := by
  decide +kernel

theorem coreCheck908_96 :
    ∀ c : Fin 1, (coreChunks908_96 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 96)) = true := by
  decide +kernel
#print axioms coreFlatten908_96
#print axioms coreCheck908_96
end Erdos883Verified
