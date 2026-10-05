import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_44 :
    (List.ofFn coreChunks908_44).flatten =
      (coreData908.take (coreResources908 44).q).drop 197 := by
  decide +kernel

theorem coreCheck908_44 :
    ∀ c : Fin 1, (coreChunks908_44 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 44)) = true := by
  decide +kernel
#print axioms coreFlatten908_44
#print axioms coreCheck908_44
end Erdos883Verified
