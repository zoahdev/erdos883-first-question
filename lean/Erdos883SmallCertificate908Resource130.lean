import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_130 :
    (List.ofFn coreChunks908_130).flatten =
      (coreData908.take (coreResources908 130).q).drop 228 := by
  decide +kernel

theorem coreCheck908_130 :
    ∀ c : Fin 1, (coreChunks908_130 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 130)) = true := by
  decide +kernel
#print axioms coreFlatten908_130
#print axioms coreCheck908_130
end Erdos883Verified
