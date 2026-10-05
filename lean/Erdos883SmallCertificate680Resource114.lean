import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_114 :
    (List.ofFn coreChunks680_114).flatten =
      (coreData680.take (coreResources680 114).q).drop 255 := by
  decide +kernel

theorem coreCheck680_114 :
    ∀ c : Fin 2, (coreChunks680_114 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 114)) = true := by
  decide +kernel
#print axioms coreFlatten680_114
#print axioms coreCheck680_114
end Erdos883Verified
