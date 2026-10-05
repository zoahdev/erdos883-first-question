import Erdos883AdaptiveSpan25027Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength25027_4 : adaptiveNumericSpans25027_4.length = 450 := by decide +kernel
theorem adaptiveSpanEvenCache25027_4 : adaptiveSpanEven25027_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain25027_4 : adaptiveSpanEven25027_4.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanEvenEntries25027_4 : adaptiveSpanEven25027_4.spans = coreEvenSpans 12514 0 adaptiveNumericSpans25027_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache25027_4 : adaptiveSpanWhole25027_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain25027_4 : adaptiveSpanWhole25027_4.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanWholeEntries25027_4 : adaptiveSpanWhole25027_4.spans = coreWholeSpans 0 adaptiveNumericSpans25027_4 := by
  decide +kernel
end Erdos883Verified
