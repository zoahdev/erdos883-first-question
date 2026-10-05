import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_68 :
    (List.ofFn coreChunks680_68).flatten =
      (coreData680.take (coreResources680 68).q).drop 128 := by
  decide +kernel

theorem coreCheck680_68 :
    ∀ c : Fin 1, (coreChunks680_68 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 68)) = true := by
  decide +kernel
#print axioms coreFlatten680_68
#print axioms coreCheck680_68
end Erdos883Verified
