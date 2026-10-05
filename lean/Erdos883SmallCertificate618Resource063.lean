import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_63 :
    (List.ofFn coreChunks618_63).flatten =
      (coreData618.take (coreResources618 63).q).drop 126 := by
  decide +kernel

theorem coreCheck618_63 :
    ∀ c : Fin 1, (coreChunks618_63 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 63)) = true := by
  decide +kernel
#print axioms coreFlatten618_63
#print axioms coreCheck618_63
end Erdos883Verified
