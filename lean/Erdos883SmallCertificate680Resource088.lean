import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_88 :
    (List.ofFn coreChunks680_88).flatten =
      (coreData680.take (coreResources680 88).q).drop 162 := by
  decide +kernel

theorem coreCheck680_88 :
    ∀ c : Fin 1, (coreChunks680_88 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 88)) = true := by
  decide +kernel
#print axioms coreFlatten680_88
#print axioms coreCheck680_88
end Erdos883Verified
