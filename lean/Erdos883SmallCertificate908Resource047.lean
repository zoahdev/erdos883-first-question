import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_47 :
    (List.ofFn coreChunks908_47).flatten =
      (coreData908.take (coreResources908 47).q).drop 200 := by
  decide +kernel

theorem coreCheck908_47 :
    ∀ c : Fin 1, (coreChunks908_47 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 47)) = true := by
  decide +kernel
#print axioms coreFlatten908_47
#print axioms coreCheck908_47
end Erdos883Verified
