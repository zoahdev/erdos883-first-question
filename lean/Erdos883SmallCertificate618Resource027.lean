import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_27 :
    (List.ofFn coreChunks618_27).flatten =
      (coreData618.take (coreResources618 27).q).drop 138 := by
  decide +kernel

theorem coreCheck618_27 :
    ∀ c : Fin 1, (coreChunks618_27 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 27)) = true := by
  decide +kernel
#print axioms coreFlatten618_27
#print axioms coreCheck618_27
end Erdos883Verified
