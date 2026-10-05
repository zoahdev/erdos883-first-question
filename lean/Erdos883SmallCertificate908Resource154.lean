import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_154 :
    (List.ofFn coreChunks908_154).flatten =
      (coreData908.take (coreResources908 154).q).drop 339 := by
  decide +kernel

theorem coreCheck908_154 :
    ∀ c : Fin 1, (coreChunks908_154 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 154)) = true := by
  decide +kernel
#print axioms coreFlatten908_154
#print axioms coreCheck908_154
end Erdos883Verified
