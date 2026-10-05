import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_159 :
    (List.ofFn coreChunks908_159).flatten =
      (coreData908.take (coreResources908 159).q).drop 371 := by
  decide +kernel

theorem coreCheck908_159 :
    ∀ c : Fin 1, (coreChunks908_159 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 159)) = true := by
  decide +kernel
#print axioms coreFlatten908_159
#print axioms coreCheck908_159
end Erdos883Verified
