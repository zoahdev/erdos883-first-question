import Erdos883AdaptiveSpan104564Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength104564_4 : adaptiveNumericSpans104564_4.length = 642 := by decide +kernel
theorem adaptiveSpanEvenCache104564_4 : adaptiveSpanEven104564_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain104564_4 : adaptiveSpanEven104564_4.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanEvenEntries104564_4 : adaptiveSpanEven104564_4.spans = coreEvenSpans 52282 0 adaptiveNumericSpans104564_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache104564_4 : adaptiveSpanWhole104564_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain104564_4 : adaptiveSpanWhole104564_4.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanWholeEntries104564_4 : adaptiveSpanWhole104564_4.spans = coreWholeSpans 0 adaptiveNumericSpans104564_4 := by
  decide +kernel
end Erdos883Verified
