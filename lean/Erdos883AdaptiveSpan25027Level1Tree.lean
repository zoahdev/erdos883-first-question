import Erdos883AdaptiveSpan25027Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength25027_1 : adaptiveNumericSpans25027_1.length = 450 := by decide +kernel
theorem adaptiveSpanEvenCache25027_1 : adaptiveSpanEven25027_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain25027_1 : adaptiveSpanEven25027_1.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanEvenEntries25027_1 : adaptiveSpanEven25027_1.spans = coreEvenSpans 12514 0 adaptiveNumericSpans25027_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache25027_1 : adaptiveSpanWhole25027_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain25027_1 : adaptiveSpanWhole25027_1.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanWholeEntries25027_1 : adaptiveSpanWhole25027_1.spans = coreWholeSpans 0 adaptiveNumericSpans25027_1 := by
  decide +kernel
end Erdos883Verified
